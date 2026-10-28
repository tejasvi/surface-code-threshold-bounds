import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4132 = true := by
  decide +kernel

theorem tot4132 : totK PA10K2 A10K2.t4132 = [0, 0, 512225982845, 1971234838531, 2014526624029, 456607259815, 12746179907, 0, 0, 0] := by
  decide +kernel

theorem rows4133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4133 = true := by
  decide +kernel

theorem tot4133 : totK PA10K2 A10K2.t4133 = [0, 0, 573825088210, 1836412170792, 1744027512211, 547058276460, 47952069846, 0, 0, 0] := by
  decide +kernel

theorem rows4134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4134 = true := by
  decide +kernel

theorem tot4134 : totK PA10K2 A10K2.t4134 = [0, 0, 282002292585, 1496008542056, 2154613841038, 783728334462, 60189116917, 0, 0, 0] := by
  decide +kernel

theorem rows4135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4135 = true := by
  decide +kernel

theorem tot4135 : totK PA10K2 A10K2.t4135 = [0, 0, 0, 521314928103, 1800754090547, 1724089906867, 466959168452, 30605747850, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
