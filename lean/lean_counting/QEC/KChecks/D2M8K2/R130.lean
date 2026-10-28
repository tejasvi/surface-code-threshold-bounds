import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t520 = true := by
  decide +kernel

theorem tot520 : totK PD2M8K2 D2M8K2.t520 = [0, 0, 241299746640, 491328169527, 149927960441, 3699256714, 0, 0] := by
  decide +kernel

theorem rows521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t521 = true := by
  decide +kernel

theorem tot521 : totK PD2M8K2 D2M8K2.t521 = [0, 0, 195688125913, 481842604757, 196853784636, 10159529672, 0, 0] := by
  decide +kernel

theorem rows522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t522 = true := by
  decide +kernel

theorem tot522 : totK PD2M8K2 D2M8K2.t522 = [0, 0, 206791432450, 478222225394, 171522070204, 9561023729, 0, 0] := by
  decide +kernel

theorem rows523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t523 = true := by
  decide +kernel

theorem tot523 : totK PD2M8K2 D2M8K2.t523 = [0, 0, 92415730560, 402788341830, 310503704517, 42072500882, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
