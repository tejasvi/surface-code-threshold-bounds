import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12112 = true := by
  decide +kernel

theorem tot12112 : totK PD2M8K2 D2M8K2.t12112 = [0, 0, 173269053777, 475181109164, 234995458571, 14255293706, 0, 0] := by
  decide +kernel

theorem rows12113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12113 = true := by
  decide +kernel

theorem tot12113 : totK PD2M8K2 D2M8K2.t12113 = [0, 0, 0, 241292903879, 492695049909, 135788883491, 2318623666, 0] := by
  decide +kernel

theorem rows12114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12114 = true := by
  decide +kernel

theorem tot12114 : totK PD2M8K2 D2M8K2.t12114 = [0, 0, 73018108289, 275976050003, 354731362137, 133980735589, 10786826731, 0] := by
  decide +kernel

theorem rows12115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12115 = true := by
  decide +kernel

theorem tot12115 : totK PD2M8K2 D2M8K2.t12115 = [0, 0, 158849285074, 477047267881, 214963411270, 11935568846, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
