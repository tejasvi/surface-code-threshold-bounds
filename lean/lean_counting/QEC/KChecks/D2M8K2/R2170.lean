import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8680 = true := by
  decide +kernel

theorem tot8680 : totK PD2M8K2 D2M8K2.t8680 = [0, 170964341809, 447244057548, 256557944046, 20171483350, 0, 0, 0] := by
  decide +kernel

theorem rows8681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8681 = true := by
  decide +kernel

theorem tot8681 : totK PD2M8K2 D2M8K2.t8681 = [0, 91352441409, 366217826468, 368566602836, 61704778555, 0, 0, 0] := by
  decide +kernel

theorem rows8682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8682 = true := by
  decide +kernel

theorem tot8682 : totK PD2M8K2 D2M8K2.t8682 = [0, 0, 294243745314, 514353811224, 95258156205, 0, 0, 0] := by
  decide +kernel

theorem rows8683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8683 = true := by
  decide +kernel

theorem tot8683 : totK PD2M8K2 D2M8K2.t8683 = [0, 176708812954, 428845751383, 253291932061, 54017692452, 2498823382, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
