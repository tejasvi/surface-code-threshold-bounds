import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5024 = true := by
  decide +kernel

theorem tot5024 : totK PD2M8K2 D2M8K2.t5024 = [0, 0, 164844387388, 452754650887, 273274140997, 29185162439, 0, 0] := by
  decide +kernel

theorem rows5025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5025 = true := by
  decide +kernel

theorem tot5025 : totK PD2M8K2 D2M8K2.t5025 = [0, 0, 215150743327, 501793376999, 193563580512, 6929530566, 0, 0] := by
  decide +kernel

theorem rows5026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5026 = true := by
  decide +kernel

theorem tot5026 : totK PD2M8K2 D2M8K2.t5026 = [0, 0, 172470406047, 463348116795, 242601054214, 18826707033, 0, 0] := by
  decide +kernel

theorem rows5027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5027 = true := by
  decide +kernel

theorem tot5027 : totK PD2M8K2 D2M8K2.t5027 = [0, 0, 180031666333, 459340560114, 245886716772, 16627933934, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
