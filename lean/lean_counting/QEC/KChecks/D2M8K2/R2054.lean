import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8216 = true := by
  decide +kernel

theorem tot8216 : totK PD2M8K2 D2M8K2.t8216 = [0, 0, 0, 222251653658, 470135836832, 162799391265, 7182288656, 0] := by
  decide +kernel

theorem rows8217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8217 = true := by
  decide +kernel

theorem tot8217 : totK PD2M8K2 D2M8K2.t8217 = [123894636495, 283213616604, 91833807012, 61133030689, 196320325547, 128761825349, 13326740810, 0] := by
  decide +kernel

theorem rows8218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8218 = true := by
  decide +kernel

theorem tot8218 : totK PD2M8K2 D2M8K2.t8218 = [193116447675, 457837488381, 234682400831, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8219 = true := by
  decide +kernel

theorem tot8219 : totK PD2M8K2 D2M8K2.t8219 = [125415013134, 442381067695, 311117493947, 28504154241, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
