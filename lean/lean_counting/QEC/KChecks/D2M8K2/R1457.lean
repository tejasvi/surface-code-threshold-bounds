import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5828 = true := by
  decide +kernel

theorem tot5828 : totK PD2M8K2 D2M8K2.t5828 = [198598261320, 480266432780, 221545565227, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5829 = true := by
  decide +kernel

theorem tot5829 : totK PD2M8K2 D2M8K2.t5829 = [52364295763, 331127661009, 427863707901, 91285177042, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows5830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5830 = true := by
  decide +kernel

theorem tot5830 : totK PD2M8K2 D2M8K2.t5830 = [0, 203961726709, 492974012163, 177838382527, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows5831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5831 = true := by
  decide +kernel

theorem tot5831 : totK PD2M8K2 D2M8K2.t5831 = [165819165509, 445064315870, 259270259855, 39264116820, 2481160468, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
