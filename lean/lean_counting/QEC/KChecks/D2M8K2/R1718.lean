import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6872 = true := by
  decide +kernel

theorem tot6872 : totK PD2M8K2 D2M8K2.t6872 = [34764112273, 320566610296, 457932388188, 92477323919, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows6873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6873 = true := by
  decide +kernel

theorem tot6873 : totK PD2M8K2 D2M8K2.t6873 = [0, 205679994540, 473516365759, 189082490773, 11856106740, 0, 0, 0] := by
  decide +kernel

theorem rows6874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6874 = true := by
  decide +kernel

theorem tot6874 : totK PD2M8K2 D2M8K2.t6874 = [170754457897, 444059066804, 264754364619, 30683114118, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6875 = true := by
  decide +kernel

theorem tot6875 : totK PD2M8K2 D2M8K2.t6875 = [178828528103, 456481148877, 239332895245, 15176982507, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
