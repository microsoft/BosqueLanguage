/*
This is an adapation of a ray tracer implementation by Luke Hoban, available at:
http://blogs.msdn.com/lukeh/archive/2007/04/03/a-ray-tracer-in-c-3-0.aspx
  
Daan Leijen has modified the coded to enable paralellization.
*/

//Further Mangled By Mark

using System;
using System.Collections.Generic;


public class Driver
{
	public static void Main(String[] args)
	{
		Scene sc = RayTracer.CreateDefaultScene();
		int[] rgbv = new int[100 * 100];
		RayTracer rt = new RayTracer(100, 100);
		rt.RenderBytes(sc, rgbv);
		rt.DisplayDiag(rgbv);
		Console.WriteLine("done!!!");
	}
}

public sealed class RayTracer
{
	private int screenWidth;
	private int screenHeight;
	private const int MaxDepth = 5;

	public RayTracer(int screenWidth, int screenHeight)
	{
		this.screenWidth = screenWidth;
		this.screenHeight = screenHeight;
	}

	internal void RenderBytes(Scene scene, Int32[] rgb)
	{
		for(int y = 0; y < screenHeight; y++)
		{
			int stride = y * screenWidth;
			Camera camera = scene.Camera;
			
			for(int x = 0; x < screenWidth; x++)
			{
				Color color = TraceRay(new Ray(camera.Pos, GetPoint(x, y, camera)), scene, 0);
				rgb[x + stride] = color.ToInt32();
			}
		}
	}

	internal void DisplayDiag(Int32[] rgb)
	{
		Console.WriteLine("Diag Pixels:");
		for(int diag = 0; diag < screenHeight; ++diag)
			Console.WriteLine(rgb[diag + diag * screenWidth]);
	}
	
	public static Scene CreateDefaultScene()
	{
		SceneObject[] things =  new SceneObject[3];
		things[0] = new Sphere(new Vector(-0.5, 1, 1.5), 0.5, Surfaces.MatteShiny);
		things[1] = new Sphere(new Vector(0, 1, -0.25), 1, Surfaces.Shiny);
		things[2] = new Plane(new Vector(0, 1, 0), 0, Surfaces.CheckerBoard);

		Light[] lights = new Light[2];
		lights[0] = new Light(new Vector(-2, 2.5, 0), new Color(.5, .45, .41));
		lights[1] = new Light(new Vector(2, 4.5, 2), new Color(.99, .95, .8));

		Camera camera = Camera.Create(new Vector(2.75, 2, 3.75), new Vector(-0.6, .5, 0));

		return new Scene(things, lights, camera);
	}

	private ISect MinIntersection(Ray ray, Scene scene)
	{
		ISect min = ISect.Null;
		foreach(SceneObject obj in scene.Things)
		{
			ISect isect = obj.Intersect(ray);
			if(!ISect.IsNull(isect))
			{
				if(ISect.IsNull(min) || min.Dist > isect.Dist)
				{
					min = isect;
				}
			}
		}
		return min;
	}

	private double TestRay(Ray ray, Scene scene)
	{
		ISect isect = MinIntersection(ray, scene);
		if(ISect.IsNull(isect))
			return 0;
		return isect.Dist;
	}

	private Color TraceRay(Ray ray, Scene scene, int depth)
	{
		ISect isect = MinIntersection(ray, scene);
		if(ISect.IsNull(isect))
			return Color.Background;
		return Shade(isect, scene, depth);
	}

	private Color GetNaturalColor(SceneObject thing, Vector pos, Vector norm, Vector rd, Scene scene)
	{
		Color ret = new Color(0, 0, 0);
		foreach(Light light in scene.Lights)
		{
			Vector ldis = Vector.Minus(light.Pos, pos);
			Vector livec = Vector.Norm(ldis);
			double neatIsect = TestRay(new Ray(pos, livec), scene);
			bool isInShadow = !((neatIsect > Vector.Mag(ldis)) || (neatIsect == 0));
			if(!isInShadow)
			{
				double illum = Vector.Dot(livec, norm);
				Color lcolor = illum > 0 ? Color.Times(illum, light.Color) : new Color(0, 0, 0);
				double specular = Vector.Dot(livec, Vector.Norm(rd));
				Color scolor = specular > 0 ? Color.Times(Math.Pow(specular, thing.Surface.Roughness), light.Color) : new Color(0, 0, 0);
				ret = Color.Plus(ret, Color.Plus(Color.Times(thing.Surface.Diffuse, lcolor), Color.Times(thing.Surface.Specular, scolor)));
			}
		}
		return ret;
	}

	private Color GetReflectionColor(SceneObject thing, Vector pos, Vector norm, Vector rd, Scene scene, int depth)
	{
		return Color.Times(thing.Surface.Reflect, TraceRay(new Ray(pos, rd), scene, depth + 1));
	}

	private Color Shade(ISect isect, Scene scene, int depth)
	{
		Vector d = isect.Ray.Dir;
		Vector pos = Vector.Plus(Vector.Times(isect.Dist, isect.Ray.Dir), isect.Ray.Start);
		Vector normal = isect.Thing.Normal(pos);
		Vector reflectDir = Vector.Minus(d, Vector.Times(2 * Vector.Dot(normal, d), normal));
		Color ret = Color.DefaultColor;
		ret = Color.Plus(ret, GetNaturalColor(isect.Thing, pos, normal, reflectDir, scene));
		if(depth >= MaxDepth)
		{
			return Color.Plus(ret, new Color(.5, .5, .5));
		}
		return Color.Plus(ret, GetReflectionColor(isect.Thing, Vector.Plus(pos, Vector.Times(.001, reflectDir)), normal, reflectDir, scene, depth));
	}

	private double RecenterX(double x)
	{
		return (x - (screenWidth / 2.0)) / (2.0 * screenWidth);
	}
	
	private double RecenterY(double y)
	{
		return -(y - (screenHeight / 2.0)) / (2.0 * screenHeight);
	}

	private Vector GetPoint(double x, double y, Camera camera)
	{
		return Vector.Norm(Vector.Plus(camera.Forward, Vector.Plus(Vector.Times(RecenterX(x), camera.Right), Vector.Times(RecenterY(y), camera.Up))));
	}
}

public static class Surfaces
{
	// Only works with X-Z plane.
	public static readonly Surface CheckerBoard = new Surface(new Color(0.02, 0.0, 0.14), new Color(1, 1, 1), .5, 150);

	public static readonly Surface Shiny = new Surface(new Color(1, 1, 1), new Color(.5, .5, .5), .7, 250);

	public static readonly Surface MatteShiny = new Surface(new Color(1, 1, 1), new Color(.25, .25, .25), .7, 250);

}

public class Vector
{
	public double X;
	public double Y;
	public double Z;

	public Vector(double x, double y, double z) 
	{ 
		X = x; 
		Y = y; 
		Z = z; 
	}
	
	public static Vector Times(double n, Vector v)
	{
		return new Vector(v.X * n, v.Y * n, v.Z * n);
	}
	
	public static Vector Minus(Vector v1, Vector v2)
	{
		return new Vector(v1.X - v2.X, v1.Y - v2.Y, v1.Z - v2.Z);
	}
	
	public static Vector Plus(Vector v1, Vector v2)
	{
		return new Vector(v1.X + v2.X, v1.Y + v2.Y, v1.Z + v2.Z);
	}
	
	public static double Dot(Vector v1, Vector v2)
	{
		return (v1.X * v2.X) + (v1.Y * v2.Y) + (v1.Z * v2.Z);
	}
	
	public static double Mag(Vector v) 
	{ return Math.Sqrt(Dot(v, v)); }
	
	public static Vector Norm(Vector v)
	{
		double mag = Mag(v);
		double div = mag == 0 ? 1000000000.0 : 1 / mag;
		return Times(div, v);
	}

	public static Vector Cross(Vector v1, Vector v2)
	{
		return new Vector(((v1.Y * v2.Z) - (v1.Z * v2.Y)), ((v1.Z * v2.X) - (v1.X * v2.Z)), ((v1.X * v2.Y) - (v1.Y * v2.X)));
	}

	public static bool Equals(Vector v1, Vector v2)
	{
		return (v1.X == v2.X) && (v1.Y == v2.Y) && (v1.Z == v2.Z);
	}
}

public class Color
{
	public double R;
	public double G;
	public double B;

	public Color(double r, double g, double b) { R = r; G = g; B = b; }
	
	public static Color Times(double n, Color v)
	{
		return new Color(n * v.R, n * v.G, n * v.B);
	}
	public static Color Times(Color v1, Color v2)
	{
		return new Color(v1.R * v2.R, v1.G * v2.G, v1.B * v2.B);
	}

	public static Color Plus(Color v1, Color v2)
	{
		return new Color(v1.R + v2.R, v1.G + v2.G, v1.B + v2.B);
	}
	public static Color Minus(Color v1, Color v2)
	{
		return new Color(v1.R - v2.R, v1.G - v2.G, v1.B - v2.B);
	}

	public static readonly Color Background = new Color(0, 0, 0);
	public static readonly Color DefaultColor = new Color(0, 0, 0);

	public static double Legalize(double d)
	{
		return d > 1 ? 1 : d;
	}

	public static Int32 ToInt32(double c)
	{
		Int32 r = (Int32)(255 * c);
		return (r > 255 ? 255 : r);
	}

	public Int32 ToInt32()
	{
		return (ToInt32(B) | ToInt32(G) << 8 | ToInt32(R) << 16 | 255 << 24);
	}
}

public class Ray
{
	public Vector Start;
	public Vector Dir;

	public Ray(Vector start, Vector dir) 
	{ 
		Start = start; 
		Dir = dir; 
	}
}

public class ISect
{
	public SceneObject Thing;
	public Ray Ray;
	public double Dist;

	public ISect(SceneObject thing, Ray ray, double dist) 
	{ 
		Thing = thing; 
		Ray = ray; 
		Dist = dist; 
	}

	public static bool IsNull(ISect sect) { return sect == null; }
	public readonly static ISect Null = null;
}

public class Surface
{
	public Color Diffuse;
	public Color Specular;
	public double Reflect;
	public double Roughness;

	public Surface(Color Diffuse, Color Specular, double Reflect, double Roughness)
	{
		this.Diffuse = Diffuse;
		this.Specular = Specular;
		this.Reflect = Reflect;
		this.Roughness = Roughness;
	}
}

public class Camera
{
	public Vector Pos;
	public Vector Forward;
	public Vector Up;
	public Vector Right;

	public Camera(Vector pos, Vector forward, Vector up, Vector right) 
	{ 
		Pos = pos; 
		Forward = forward; 
		Up = up; 
		Right = right; 
	}

	public static Camera Create(Vector pos, Vector lookAt)
	{
		Vector forward = Vector.Norm(Vector.Minus(lookAt, pos));
		Vector down = new Vector(0, -1, 0);
		Vector right = Vector.Times(1.5, Vector.Norm(Vector.Cross(forward, down)));
		Vector up = Vector.Times(1.5, Vector.Norm(Vector.Cross(forward, right)));

		return new Camera(pos, forward, up, right);
	}
}

public class Light
{
	public Vector Pos;
	public Color Color;

	public Light(Vector pos, Color color) 
	{ 
		Pos = pos; 
		Color = color; 
	}
}

public abstract class SceneObject
{
	public Surface Surface;
	public abstract ISect Intersect(Ray ray);
	public abstract Vector Normal(Vector pos);

	public SceneObject(Surface surface) { Surface = surface; }
}

public class Sphere : SceneObject
{
	public Vector Center;
	public double Radius;

	public Sphere(Vector center, double radius, Surface surface)
		: base(surface)
	{
		Center = center;
		Radius = radius;
	}

	public override ISect Intersect(Ray ray)
	{
		Vector eo = Vector.Minus(Center, ray.Start);
		double v = Vector.Dot(eo, ray.Dir);
		double dist;
		
		if(v < 0)
		{
			dist = 0;
		}
		else
		{
			double disc = Math.Pow(Radius, 2) - (Vector.Dot(eo, eo) - Math.Pow(v, 2));
			dist = disc < 0 ? 0 : v - Math.Sqrt(disc);
		}

		if(dist == 0) 
			return ISect.Null;
		
		return new ISect(this, ray, dist);
	}

	public override Vector Normal(Vector pos)
	{
		return Vector.Norm(Vector.Minus(pos, Center));
	}
}

public class Plane : SceneObject
{
	public Vector Norm;
	public double Offset;

	public Plane(Vector norm, double offset, Surface surface)
		: base(surface)
	{
		Norm = norm;
		Offset = offset;
	}

	public override ISect Intersect(Ray ray)
	{
		double denom = Vector.Dot(Norm, ray.Dir);

		if(denom > 0)
			return ISect.Null;

		return new ISect(this, ray, (Vector.Dot(Norm, ray.Start) + Offset) / (-denom));
	}

	public override Vector Normal(Vector pos)
	{
		return Norm;
	}
}

public class Scene
{
	public SceneObject[] Things;
	public Light[] Lights;
	public Camera Camera;

	public Scene(SceneObject[] things, Light[] lights, Camera camera)
	{
		Things = things; 
		Lights = lights; 
		Camera = camera;
	}
}


