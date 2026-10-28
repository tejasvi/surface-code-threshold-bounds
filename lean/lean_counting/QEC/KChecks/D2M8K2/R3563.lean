import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14252 = true := by
  decide +kernel

theorem tot14252 : totK PD2M8K2 D2M8K2.t14252 = [0, 211794167594, 485794246074, 185491169092, 5047579416, 0, 0, 0] := by
  decide +kernel

theorem rows14253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14253 = true := by
  decide +kernel

theorem tot14253 : totK PD2M8K2 D2M8K2.t14253 = [0, 166022840475, 448836428581, 254065870263, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows14254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14254 = true := by
  decide +kernel

theorem tot14254 : totK PD2M8K2 D2M8K2.t14254 = [0, 92025651062, 370498589341, 336670556385, 56950542398, 1095107716, 0, 0] := by
  decide +kernel

theorem rows14255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14255 = true := by
  decide +kernel

theorem tot14255 : totK PD2M8K2 D2M8K2.t14255 = [0, 0, 328766806296, 475441251133, 73361002202, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
