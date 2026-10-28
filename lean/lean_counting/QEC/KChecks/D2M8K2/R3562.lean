import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14248 = true := by
  decide +kernel

theorem tot14248 : totK PD2M8K2 D2M8K2.t14248 = [0, 171849545556, 443919244165, 267289634634, 29170585304, 0, 0, 0] := by
  decide +kernel

theorem rows14249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14249 = true := by
  decide +kernel

theorem tot14249 : totK PD2M8K2 D2M8K2.t14249 = [0, 171522422574, 487962779533, 241425153199, 11285325467, 0, 0, 0] := by
  decide +kernel

theorem rows14250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14250 = true := by
  decide +kernel

theorem tot14250 : totK PD2M8K2 D2M8K2.t14250 = [0, 181409114965, 459717097664, 236256533798, 15500433850, 0, 0, 0] := by
  decide +kernel

theorem rows14251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14251 = true := by
  decide +kernel

theorem tot14251 : totK PD2M8K2 D2M8K2.t14251 = [0, 190200641554, 479161790663, 219013855000, 12370590376, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
