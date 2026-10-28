import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5248 = true := by
  decide +kernel

theorem tot5248 : totK PD2M8K2 D2M8K2.t5248 = [0, 198186192346, 472099716734, 238040156541, 13773507857, 0, 0, 0] := by
  decide +kernel

theorem rows5249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5249 = true := by
  decide +kernel

theorem tot5249 : totK PD2M8K2 D2M8K2.t5249 = [0, 40106611963, 396432066192, 441771976868, 53401614604, 0, 0, 0] := by
  decide +kernel

theorem rows5250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5250 = true := by
  decide +kernel

theorem tot5250 : totK PD2M8K2 D2M8K2.t5250 = [0, 109366012991, 352061921836, 346835889272, 92817683866, 2575744806, 0, 0] := by
  decide +kernel

theorem rows5251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5251 = true := by
  decide +kernel

theorem tot5251 : totK PD2M8K2 D2M8K2.t5251 = [0, 174805875644, 445478685245, 272375383657, 30158397190, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
