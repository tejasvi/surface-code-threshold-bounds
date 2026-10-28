import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4480 = true := by
  decide +kernel

theorem tot4480 : totK PA10K2 A10K2.t4480 = [515062303593, 1828261770222, 1953175213968, 673405854924, 65502523519, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4481 = true := by
  decide +kernel

theorem tot4481 : totK PA10K2 A10K2.t4481 = [297267720674, 1423439627398, 2156840515928, 962790757003, 83585627410, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4482 = true := by
  decide +kernel

theorem tot4482 : totK PA10K2 A10K2.t4482 = [0, 542361209589, 1914666068292, 1908971013553, 504538901125, 31747192500, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4483 = true := by
  decide +kernel

theorem tot4483 : totK PA10K2 A10K2.t4483 = [517935020351, 1821953926889, 2015088885557, 745796316392, 78892481013, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
