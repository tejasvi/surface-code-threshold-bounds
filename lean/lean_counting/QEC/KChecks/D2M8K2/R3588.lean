import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14352 = true := by
  decide +kernel

theorem tot14352 : totK PD2M8K2 D2M8K2.t14352 = [0, 187712244605, 464480328270, 239411454428, 16750524228, 0, 0, 0] := by
  decide +kernel

theorem rows14353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14353 = true := by
  decide +kernel

theorem tot14353 : totK PD2M8K2 D2M8K2.t14353 = [0, 81435252978, 348847129554, 387057296905, 84471443443, 1164319620, 0, 0] := by
  decide +kernel

theorem rows14354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14354 = true := by
  decide +kernel

theorem tot14354 : totK PD2M8K2 D2M8K2.t14354 = [0, 0, 228502422303, 493040782990, 161453345793, 9404247146, 0, 0] := by
  decide +kernel

theorem rows14355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14355 = true := by
  decide +kernel

theorem tot14355 : totK PD2M8K2 D2M8K2.t14355 = [0, 153875073329, 391500055872, 279536154081, 56696623967, 2481160468, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
