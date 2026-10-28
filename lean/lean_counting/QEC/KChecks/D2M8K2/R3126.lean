import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12504 = true := by
  decide +kernel

theorem tot12504 : totK PD2M8K2 D2M8K2.t12504 = [0, 188655335925, 480726445686, 222898292611, 12287346641, 0, 0, 0] := by
  decide +kernel

theorem rows12505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12505 = true := by
  decide +kernel

theorem tot12505 : totK PD2M8K2 D2M8K2.t12505 = [0, 0, 236490726040, 476330470598, 194996677799, 11701455490, 0, 0] := by
  decide +kernel

theorem rows12506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12506 = true := by
  decide +kernel

theorem tot12506 : totK PD2M8K2 D2M8K2.t12506 = [0, 50840018711, 226799971760, 427650237003, 185816006850, 3707914794, 0, 0] := by
  decide +kernel

theorem rows12507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12507 = true := by
  decide +kernel

theorem tot12507 : totK PD2M8K2 D2M8K2.t12507 = [0, 194826169280, 462766258607, 241949412955, 21049420686, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
