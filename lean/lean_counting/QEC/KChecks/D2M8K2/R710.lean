import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2840 = true := by
  decide +kernel

theorem tot2840 : totK PD2M8K2 D2M8K2.t2840 = [0, 172185734829, 474976052029, 227856537018, 12488348436, 0, 0, 0] := by
  decide +kernel

theorem rows2841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2841 = true := by
  decide +kernel

theorem tot2841 : totK PD2M8K2 D2M8K2.t2841 = [0, 182748149967, 444792534282, 274382778222, 33531500665, 0, 0, 0] := by
  decide +kernel

theorem rows2842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2842 = true := by
  decide +kernel

theorem tot2842 : totK PD2M8K2 D2M8K2.t2842 = [0, 186290647778, 474152740879, 237097611956, 10971206243, 0, 0, 0] := by
  decide +kernel

theorem rows2843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2843 = true := by
  decide +kernel

theorem tot2843 : totK PD2M8K2 D2M8K2.t2843 = [0, 74970153138, 310803472494, 367376727223, 152423800114, 17176948997, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
