import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5412 = true := by
  decide +kernel

theorem tot5412 : totK PD2M8K2 D2M8K2.t5412 = [0, 0, 119321516575, 341444065721, 293461830483, 131446317644, 11406585291, 0] := by
  decide +kernel

theorem rows5413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5413 = true := by
  decide +kernel

theorem tot5413 : totK PD2M8K2 D2M8K2.t5413 = [0, 0, 256326113575, 468472139390, 170952673080, 9744212013, 0, 0] := by
  decide +kernel

theorem rows5414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5414 = true := by
  decide +kernel

theorem tot5414 : totK PD2M8K2 D2M8K2.t5414 = [0, 0, 0, 307082012973, 480697731677, 88147271689, 1369150432, 0] := by
  decide +kernel

theorem rows5415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5415 = true := by
  decide +kernel

theorem tot5415 : totK PD2M8K2 D2M8K2.t5415 = [0, 0, 122823664054, 394278245214, 359172008643, 48254259815, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
