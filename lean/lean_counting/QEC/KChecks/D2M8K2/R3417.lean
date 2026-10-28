import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13668 = true := by
  decide +kernel

theorem tot13668 : totK PD2M8K2 D2M8K2.t13668 = [0, 180939287263, 470088454545, 248726747178, 13735513938, 0, 0, 0] := by
  decide +kernel

theorem rows13669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13669 = true := by
  decide +kernel

theorem tot13669 : totK PD2M8K2 D2M8K2.t13669 = [0, 0, 288448813979, 491176138403, 106534025511, 1242138600, 0, 0] := by
  decide +kernel

theorem rows13670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13670 = true := by
  decide +kernel

theorem tot13670 : totK PD2M8K2 D2M8K2.t13670 = [0, 0, 181222723314, 473099176799, 197229656132, 8407946489, 0, 0] := by
  decide +kernel

theorem rows13671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13671 = true := by
  decide +kernel

theorem tot13671 : totK PD2M8K2 D2M8K2.t13671 = [0, 179733180668, 421397426150, 207300363015, 80169351606, 12101082977, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
