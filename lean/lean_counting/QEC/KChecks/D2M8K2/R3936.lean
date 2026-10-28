import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15744 = true := by
  decide +kernel

theorem tot15744 : totK PD2M8K2 D2M8K2.t15744 = [0, 0, 0, 15833379882, 337075462765, 442562561105, 77047638429, 1162935789] := by
  decide +kernel

theorem rows15745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15745 = true := by
  decide +kernel

theorem tot15745 : totK PD2M8K2 D2M8K2.t15745 = [0, 0, 0, 80804128693, 314436932045, 360836468870, 101267787156, 4232192998] := by
  decide +kernel

theorem rows15746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15746 = true := by
  decide +kernel

theorem tot15746 : totK PD2M8K2 D2M8K2.t15746 = [0, 0, 0, 237233620882, 458832098313, 166657148330, 7546181695, 0] := by
  decide +kernel

theorem rows15747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15747 = true := by
  decide +kernel

theorem tot15747 : totK PD2M8K2 D2M8K2.t15747 = [0, 0, 0, 211625766952, 490968618096, 159638235473, 5211738191, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
