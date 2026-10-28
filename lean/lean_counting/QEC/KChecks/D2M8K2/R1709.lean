import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6836 = true := by
  decide +kernel

theorem tot6836 : totK PD2M8K2 D2M8K2.t6836 = [122769857598, 390489085747, 369078445542, 48420717157, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6837 = true := by
  decide +kernel

theorem tot6837 : totK PD2M8K2 D2M8K2.t6837 = [196940960041, 483595567014, 220856114641, 14520949525, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6838 = true := by
  decide +kernel

theorem tot6838 : totK PD2M8K2 D2M8K2.t6838 = [88459214294, 384804304981, 357080682899, 75279430699, 10443687594, 0, 0, 0] := by
  decide +kernel

theorem rows6839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6839 = true := by
  decide +kernel

theorem tot6839 : totK PD2M8K2 D2M8K2.t6839 = [0, 157387447848, 451344607456, 275924351287, 17761389896, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
