import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4856 = true := by
  decide +kernel

theorem tot4856 : totK PD2M8K2 D2M8K2.t4856 = [0, 0, 84771917110, 374134653254, 357047206858, 59416398135, 1369150432, 0] := by
  decide +kernel

theorem rows4857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4857 = true := by
  decide +kernel

theorem tot4857 : totK PD2M8K2 D2M8K2.t4857 = [0, 0, 19982995165, 315415094704, 490652078795, 67934372461, 0, 0] := by
  decide +kernel

theorem rows4858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4858 = true := by
  decide +kernel

theorem tot4858 : totK PD2M8K2 D2M8K2.t4858 = [0, 0, 176703360121, 456757963262, 266908596506, 26467404799, 0, 0] := by
  decide +kernel

theorem rows4859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4859 = true := by
  decide +kernel

theorem tot4859 : totK PD2M8K2 D2M8K2.t4859 = [0, 0, 195223175679, 475067985157, 220657118533, 12366815362, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
