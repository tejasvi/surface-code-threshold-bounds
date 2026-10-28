import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6520 = true := by
  decide +kernel

theorem tot6520 : totK PD2M8K2 D2M8K2.t6520 = [67531417387, 336285589715, 416185362287, 88797968568, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows6521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6521 = true := by
  decide +kernel

theorem tot6521 : totK PD2M8K2 D2M8K2.t6521 = [0, 214584184170, 491405761475, 171266156044, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows6522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6522 = true := by
  decide +kernel

theorem tot6522 : totK PD2M8K2 D2M8K2.t6522 = [172463793344, 436047877267, 250382279558, 42373356700, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows6523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6523 = true := by
  decide +kernel

theorem tot6523 : totK PD2M8K2 D2M8K2.t6523 = [159893884193, 439002147084, 283689319286, 30251837770, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
