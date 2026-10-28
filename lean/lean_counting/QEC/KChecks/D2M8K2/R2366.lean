import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9464 = true := by
  decide +kernel

theorem tot9464 : totK PD2M8K2 D2M8K2.t9464 = [0, 150669819809, 451570897683, 257339447693, 16087094179, 0, 0, 0] := by
  decide +kernel

theorem rows9465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9465 = true := by
  decide +kernel

theorem tot9465 : totK PD2M8K2 D2M8K2.t9465 = [0, 211988033317, 480674696209, 207600018664, 10460607274, 0, 0, 0] := by
  decide +kernel

theorem rows9466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9466 = true := by
  decide +kernel

theorem tot9466 : totK PD2M8K2 D2M8K2.t9466 = [0, 197669362334, 462659260210, 213009339823, 12319708528, 0, 0, 0] := by
  decide +kernel

theorem rows9467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9467 = true := by
  decide +kernel

theorem tot9467 : totK PD2M8K2 D2M8K2.t9467 = [0, 157413912048, 465268975923, 243199576851, 16077659409, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
