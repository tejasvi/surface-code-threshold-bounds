import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6408 = true := by
  decide +kernel

theorem tot6408 : totK PA10K2 A10K2.t6408 = [0, 478719733682, 1789079100424, 1838646137928, 501998181329, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6409 = true := by
  decide +kernel

theorem tot6409 : totK PA10K2 A10K2.t6409 = [423713582285, 1603922593178, 1967978621354, 854294940351, 85720966527, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6410 = true := by
  decide +kernel

theorem tot6410 : totK PA10K2 A10K2.t6410 = [99047224469, 1051781721171, 2202007563918, 1151561693632, 107675365220, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6411 = true := by
  decide +kernel

theorem tot6411 : totK PA10K2 A10K2.t6411 = [501990865574, 1736686258014, 1883783709521, 748921670869, 151445267013, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
