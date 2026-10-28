import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9056 = true := by
  decide +kernel

theorem tot9056 : totK PD2M8K2 D2M8K2.t9056 = [0, 65968244593, 289556685675, 391923155883, 122745164809, 5972970333, 0, 0] := by
  decide +kernel

theorem rows9057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9057 = true := by
  decide +kernel

theorem tot9057 : totK PD2M8K2 D2M8K2.t9057 = [0, 167381374111, 456156960340, 264518352797, 26721590917, 0, 0, 0] := by
  decide +kernel

theorem rows9058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9058 = true := by
  decide +kernel

theorem tot9058 : totK PD2M8K2 D2M8K2.t9058 = [0, 177550997700, 475086053589, 234979159225, 12104726141, 0, 0, 0] := by
  decide +kernel

theorem rows9059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9059 = true := by
  decide +kernel

theorem tot9059 : totK PD2M8K2 D2M8K2.t9059 = [0, 0, 328319679911, 512161310025, 71385340726, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
