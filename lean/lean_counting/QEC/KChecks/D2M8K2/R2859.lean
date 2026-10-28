import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11436 = true := by
  decide +kernel

theorem tot11436 : totK PD2M8K2 D2M8K2.t11436 = [0, 0, 170460545821, 453812313722, 263331831472, 25368447013, 0, 0] := by
  decide +kernel

theorem rows11437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11437 = true := by
  decide +kernel

theorem tot11437 : totK PD2M8K2 D2M8K2.t11437 = [0, 0, 200767152311, 490198181586, 190496692872, 5362199427, 0, 0] := by
  decide +kernel

theorem rows11438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11438 = true := by
  decide +kernel

theorem tot11438 : totK PD2M8K2 D2M8K2.t11438 = [0, 171648477473, 399595658952, 229339174566, 95035859070, 6756679742, 0, 0] := by
  decide +kernel

theorem rows11439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11439 = true := by
  decide +kernel

theorem tot11439 : totK PD2M8K2 D2M8K2.t11439 = [0, 180221153740, 459568833738, 252400449191, 18044947519, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
