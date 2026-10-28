import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14492 = true := by
  decide +kernel

theorem tot14492 : totK PD2M8K2 D2M8K2.t14492 = [0, 170734000241, 464587137865, 270383392282, 24240208755, 0, 0, 0] := by
  decide +kernel

theorem rows14493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14493 = true := by
  decide +kernel

theorem tot14493 : totK PD2M8K2 D2M8K2.t14493 = [0, 179238291557, 462960902905, 250841735097, 15849203835, 0, 0, 0] := by
  decide +kernel

theorem rows14494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14494 = true := by
  decide +kernel

theorem tot14494 : totK PD2M8K2 D2M8K2.t14494 = [0, 0, 297424404017, 484245345184, 113541119002, 1238673482, 0, 0] := by
  decide +kernel

theorem rows14495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14495 = true := by
  decide +kernel

theorem tot14495 : totK PD2M8K2 D2M8K2.t14495 = [71933061318, 99622542677, 153240407667, 380712955382, 167853429316, 8063697217, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
