import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10628 = true := by
  decide +kernel

theorem tot10628 : totK PD2M8K2 D2M8K2.t10628 = [0, 104508824815, 324046787555, 328941364817, 147986510900, 11712179621, 0, 0] := by
  decide +kernel

theorem rows10629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10629 = true := by
  decide +kernel

theorem tot10629 : totK PD2M8K2 D2M8K2.t10629 = [0, 177006099646, 454994198599, 232402213674, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows10630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10630 = true := by
  decide +kernel

theorem tot10630 : totK PD2M8K2 D2M8K2.t10630 = [0, 127232457136, 428877026467, 294650481075, 26637285155, 0, 0, 0] := by
  decide +kernel

theorem rows10631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10631 = true := by
  decide +kernel

theorem tot10631 : totK PD2M8K2 D2M8K2.t10631 = [0, 0, 271845605565, 505691189913, 108232161746, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
