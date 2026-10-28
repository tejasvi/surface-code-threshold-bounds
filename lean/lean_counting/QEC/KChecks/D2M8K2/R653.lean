import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2612 = true := by
  decide +kernel

theorem tot2612 : totK PD2M8K2 D2M8K2.t2612 = [0, 191156383370, 465298444774, 243221602776, 20884098803, 0, 0, 0] := by
  decide +kernel

theorem rows2613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2613 = true := by
  decide +kernel

theorem tot2613 : totK PD2M8K2 D2M8K2.t2613 = [0, 156825935717, 465238347530, 259029063472, 15838615807, 0, 0, 0] := by
  decide +kernel

theorem rows2614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2614 = true := by
  decide +kernel

theorem tot2614 : totK PD2M8K2 D2M8K2.t2614 = [0, 0, 276949904225, 485149209405, 105080588667, 2160984415, 0, 0] := by
  decide +kernel

theorem rows2615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2615 = true := by
  decide +kernel

theorem tot2615 : totK PD2M8K2 D2M8K2.t2615 = [0, 102015507908, 374912314649, 330310417649, 70798701313, 2770420231, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
