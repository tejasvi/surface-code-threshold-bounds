import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1940 = true := by
  decide +kernel

theorem tot1940 : totK PA10K2 A10K2.t1940 = [0, 0, 269934058022, 1382777216559, 2189930745807, 1108175279004, 116043165288, 0, 0, 0] := by
  decide +kernel

theorem rows1941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1941 = true := by
  decide +kernel

theorem tot1941 : totK PA10K2 A10K2.t1941 = [0, 0, 139103737231, 802654098817, 1877488450733, 1669131026191, 369927804241, 13572172291, 0, 0] := by
  decide +kernel

theorem rows1942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1942 = true := by
  decide +kernel

theorem tot1942 : totK PA10K2 A10K2.t1942 = [0, 0, 499541122132, 1852756740166, 2048884315440, 609837615935, 30462250827, 0, 0, 0] := by
  decide +kernel

theorem rows1943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1943 = true := by
  decide +kernel

theorem tot1943 : totK PA10K2 A10K2.t1943 = [0, 0, 227811217789, 1236696631912, 2112738955090, 1210878159442, 188392737546, 6281495166, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
