import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5676 = true := by
  decide +kernel

theorem tot5676 : totK PD2M8K2 D2M8K2.t5676 = [0, 0, 325909751405, 509858539661, 70954842566, 0, 0, 0] := by
  decide +kernel

theorem rows5677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5677 = true := by
  decide +kernel

theorem tot5677 : totK PD2M8K2 D2M8K2.t5677 = [0, 191546648453, 456480769457, 247310848043, 20281206627, 0, 0, 0] := by
  decide +kernel

theorem rows5678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5678 = true := by
  decide +kernel

theorem tot5678 : totK PD2M8K2 D2M8K2.t5678 = [0, 182199284495, 461496341170, 227033487041, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows5679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5679 = true := by
  decide +kernel

theorem tot5679 : totK PD2M8K2 D2M8K2.t5679 = [0, 44671396901, 321012581383, 444097361783, 85919366742, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
