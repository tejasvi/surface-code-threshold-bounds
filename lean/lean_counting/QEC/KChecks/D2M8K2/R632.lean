import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2528 = true := by
  decide +kernel

theorem tot2528 : totK PD2M8K2 D2M8K2.t2528 = [0, 284071543058, 513748037154, 104946704507, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows2529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2529 = true := by
  decide +kernel

theorem tot2529 : totK PD2M8K2 D2M8K2.t2529 = [113895582449, 341688109197, 328358041260, 93997664492, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows2530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2530 = true := by
  decide +kernel

theorem tot2530 : totK PD2M8K2 D2M8K2.t2530 = [191190287631, 449558252087, 256347089246, 27429469956, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2531 = true := by
  decide +kernel

theorem tot2531 : totK PD2M8K2 D2M8K2.t2531 = [111297231288, 427198914005, 335437620725, 30053466698, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
