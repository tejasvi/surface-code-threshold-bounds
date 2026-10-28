import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5192 = true := by
  decide +kernel

theorem tot5192 : totK PD2M8K2 D2M8K2.t5192 = [0, 0, 79989490309, 266353243221, 382824398716, 142812139142, 10830574984, 0] := by
  decide +kernel

theorem rows5193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5193 = true := by
  decide +kernel

theorem tot5193 : totK PD2M8K2 D2M8K2.t5193 = [0, 0, 182836418868, 464793816715, 250906575033, 22592168133, 0, 0] := by
  decide +kernel

theorem rows5194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5194 = true := by
  decide +kernel

theorem tot5194 : totK PD2M8K2 D2M8K2.t5194 = [0, 0, 180758428870, 465273367995, 242551517094, 17104814242, 0, 0] := by
  decide +kernel

theorem rows5195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5195 = true := by
  decide +kernel

theorem tot5195 : totK PD2M8K2 D2M8K2.t5195 = [0, 0, 0, 308220940461, 494666948531, 91916634120, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
