import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5144 = true := by
  decide +kernel

theorem tot5144 : totK PA10K2 A10K2.t5144 = [0, 0, 990761343062, 2428615544611, 1203550742367, 107967786921, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5145 = true := by
  decide +kernel

theorem tot5145 : totK PA10K2 A10K2.t5145 = [0, 0, 478468022973, 1793416058180, 1878375535448, 487204144500, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows5146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5146 = true := by
  decide +kernel

theorem tot5146 : totK PA10K2 A10K2.t5146 = [0, 0, 581999584315, 1977680491443, 1832707986135, 384465090950, 12718857877, 0, 0, 0] := by
  decide +kernel

theorem rows5147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5147 = true := by
  decide +kernel

theorem tot5147 : totK PA10K2 A10K2.t5147 = [0, 0, 449137901196, 1740019952862, 1954830399913, 530622493564, 32470943963, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
