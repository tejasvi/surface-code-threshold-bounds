import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13628 = true := by
  decide +kernel

theorem tot13628 : totK PD2M8K2 D2M8K2.t13628 = [0, 177094433147, 471754700629, 235105656872, 12119328803, 0, 0, 0] := by
  decide +kernel

theorem rows13629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13629 = true := by
  decide +kernel

theorem tot13629 : totK PD2M8K2 D2M8K2.t13629 = [0, 210897138771, 478597529377, 192399413561, 6812087456, 0, 0, 0] := by
  decide +kernel

theorem rows13630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13630 = true := by
  decide +kernel

theorem tot13630 : totK PD2M8K2 D2M8K2.t13630 = [0, 182434567684, 442322757176, 237772806101, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows13631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13631 = true := by
  decide +kernel

theorem tot13631 : totK PD2M8K2 D2M8K2.t13631 = [0, 91962125627, 402180136293, 323311168898, 42727500699, 1095107716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
