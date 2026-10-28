import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3592 = true := by
  decide +kernel

theorem tot3592 : totK PD2M8K2 D2M8K2.t3592 = [0, 0, 155570583904, 464038653393, 220297321965, 13409817603, 0, 0] := by
  decide +kernel

theorem rows3593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3593 = true := by
  decide +kernel

theorem tot3593 : totK PD2M8K2 D2M8K2.t3593 = [0, 0, 0, 321190971394, 431414030997, 77734020383, 1209030869, 0] := by
  decide +kernel

theorem rows3594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3594 = true := by
  decide +kernel

theorem tot3594 : totK PD2M8K2 D2M8K2.t3594 = [0, 0, 192446760530, 478138190140, 196814659565, 10196273897, 0, 0] := by
  decide +kernel

theorem rows3595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3595 = true := by
  decide +kernel

theorem tot3595 : totK PD2M8K2 D2M8K2.t3595 = [0, 0, 196389381959, 469757907215, 195780820210, 12177165453, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
