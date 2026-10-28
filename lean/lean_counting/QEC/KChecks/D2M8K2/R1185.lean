import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4740 = true := by
  decide +kernel

theorem tot4740 : totK PD2M8K2 D2M8K2.t4740 = [0, 0, 0, 282312652259, 479127170872, 86640955177, 1239866073, 0] := by
  decide +kernel

theorem rows4741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4741 = true := by
  decide +kernel

theorem tot4741 : totK PD2M8K2 D2M8K2.t4741 = [0, 0, 127856504783, 416769941189, 343441674605, 38809089061, 0, 0] := by
  decide +kernel

theorem rows4742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4742 = true := by
  decide +kernel

theorem tot4742 : totK PD2M8K2 D2M8K2.t4742 = [0, 0, 207555767563, 476301336307, 215787089431, 12583462246, 0, 0] := by
  decide +kernel

theorem rows4743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4743 = true := by
  decide +kernel

theorem tot4743 : totK PD2M8K2 D2M8K2.t4743 = [0, 0, 173287831485, 466614505869, 240192179205, 15671754440, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
