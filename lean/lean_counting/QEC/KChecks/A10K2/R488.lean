import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1952 = true := by
  decide +kernel

theorem tot1952 : totK PA10K2 A10K2.t1952 = [0, 0, 535713900117, 1971464114048, 2085239489856, 524110997544, 19707287507, 0, 0, 0] := by
  decide +kernel

theorem rows1953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1953 = true := by
  decide +kernel

theorem tot1953 : totK PA10K2 A10K2.t1953 = [0, 0, 415052191125, 1619874859412, 2014805643486, 758217468394, 68939555567, 0, 0, 0] := by
  decide +kernel

theorem rows1954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1954 = true := by
  decide +kernel

theorem tot1954 : totK PA10K2 A10K2.t1954 = [0, 0, 395161385929, 1695952406737, 2062191920184, 702575007243, 49696803124, 0, 0, 0] := by
  decide +kernel

theorem rows1955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1955 = true := by
  decide +kernel

theorem tot1955 : totK PA10K2 A10K2.t1955 = [0, 0, 0, 505952627640, 1798806345975, 1717012163003, 475885115004, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
