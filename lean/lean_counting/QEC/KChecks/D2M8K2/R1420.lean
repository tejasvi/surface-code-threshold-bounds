import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5680 = true := by
  decide +kernel

theorem tot5680 : totK PD2M8K2 D2M8K2.t5680 = [0, 0, 203358532039, 467783841787, 167549893148, 11727338389, 0, 0] := by
  decide +kernel

theorem rows5681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5681 = true := by
  decide +kernel

theorem tot5681 : totK PD2M8K2 D2M8K2.t5681 = [0, 173468932483, 444229774320, 258958560920, 23540461171, 0, 0, 0] := by
  decide +kernel

theorem rows5682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5682 = true := by
  decide +kernel

theorem tot5682 : totK PD2M8K2 D2M8K2.t5682 = [0, 178785228653, 455514197058, 226055404308, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows5683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5683 = true := by
  decide +kernel

theorem tot5683 : totK PD2M8K2 D2M8K2.t5683 = [0, 45772753867, 318217476135, 436531134081, 86586919189, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
