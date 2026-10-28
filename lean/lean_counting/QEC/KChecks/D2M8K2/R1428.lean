import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5712 = true := by
  decide +kernel

theorem tot5712 : totK PD2M8K2 D2M8K2.t5712 = [0, 172341156901, 457784878677, 265480900952, 31850407658, 0, 0, 0] := by
  decide +kernel

theorem rows5713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5713 = true := by
  decide +kernel

theorem tot5713 : totK PD2M8K2 D2M8K2.t5713 = [0, 179722208364, 461670527506, 248002536545, 16045553671, 0, 0, 0] := by
  decide +kernel

theorem rows5714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5714 = true := by
  decide +kernel

theorem tot5714 : totK PD2M8K2 D2M8K2.t5714 = [0, 88063885426, 345262898486, 384259643674, 75255666314, 1164319620, 0, 0] := by
  decide +kernel

theorem rows5715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5715 = true := by
  decide +kernel

theorem tot5715 : totK PD2M8K2 D2M8K2.t5715 = [0, 0, 253559100415, 495689050294, 145660394902, 8423393484, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
