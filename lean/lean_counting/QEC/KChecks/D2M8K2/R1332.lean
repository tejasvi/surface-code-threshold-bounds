import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5328 = true := by
  decide +kernel

theorem tot5328 : totK PD2M8K2 D2M8K2.t5328 = [0, 0, 179771020165, 459834787371, 225628304908, 17381584168, 0, 0] := by
  decide +kernel

theorem rows5329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5329 = true := by
  decide +kernel

theorem tot5329 : totK PD2M8K2 D2M8K2.t5329 = [0, 0, 204254104428, 486045411896, 194193355791, 9713690252, 0, 0] := by
  decide +kernel

theorem rows5330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5330 = true := by
  decide +kernel

theorem tot5330 : totK PD2M8K2 D2M8K2.t5330 = [0, 0, 86383660598, 362853721327, 350122327124, 58886935745, 1239866073, 0] := by
  decide +kernel

theorem rows5331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5331 = true := by
  decide +kernel

theorem tot5331 : totK PD2M8K2 D2M8K2.t5331 = [0, 0, 56272127618, 370214026039, 423431315354, 47679921519, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
