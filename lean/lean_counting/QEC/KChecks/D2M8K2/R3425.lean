import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13700 = true := by
  decide +kernel

theorem tot13700 : totK PD2M8K2 D2M8K2.t13700 = [0, 0, 172244067394, 459639328102, 205682635538, 16562973755, 0, 0] := by
  decide +kernel

theorem rows13701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13701 = true := by
  decide +kernel

theorem tot13701 : totK PD2M8K2 D2M8K2.t13701 = [0, 0, 239504473545, 491721279473, 160324127202, 5241237773, 0, 0] := by
  decide +kernel

theorem rows13702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13702 = true := by
  decide +kernel

theorem tot13702 : totK PD2M8K2 D2M8K2.t13702 = [0, 0, 176556796213, 481297237229, 207247345160, 10438333833, 0, 0] := by
  decide +kernel

theorem rows13703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13703 = true := by
  decide +kernel

theorem tot13703 : totK PD2M8K2 D2M8K2.t13703 = [0, 179595312347, 441934898258, 216381760505, 53234442147, 9516380681, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
