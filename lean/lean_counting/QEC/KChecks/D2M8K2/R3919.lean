import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15676 = true := by
  decide +kernel

theorem tot15676 : totK PD2M8K2 D2M8K2.t15676 = [0, 0, 102957601977, 426205609148, 333001229425, 30577234683, 0, 0] := by
  decide +kernel

theorem rows15677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15677 = true := by
  decide +kernel

theorem tot15677 : totK PD2M8K2 D2M8K2.t15677 = [0, 0, 0, 281749499812, 513508110191, 96207087910, 1369150432, 0] := by
  decide +kernel

theorem rows15678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15678 = true := by
  decide +kernel

theorem tot15678 : totK PD2M8K2 D2M8K2.t15678 = [0, 0, 158559633009, 443887917737, 276594861862, 27269043583, 0, 0] := by
  decide +kernel

theorem rows15679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15679 = true := by
  decide +kernel

theorem tot15679 : totK PD2M8K2 D2M8K2.t15679 = [0, 0, 173973661533, 456914432420, 233269835666, 13614672882, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
