import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1684 = true := by
  decide +kernel

theorem tot1684 : totK PD2M8K2 D2M8K2.t1684 = [0, 0, 154698954605, 433600029728, 278273563382, 23185501179, 0, 0] := by
  decide +kernel

theorem rows1685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1685 = true := by
  decide +kernel

theorem tot1685 : totK PD2M8K2 D2M8K2.t1685 = [0, 0, 192246125636, 458841651363, 219320760740, 12523541424, 0, 0] := by
  decide +kernel

theorem rows1686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1686 = true := by
  decide +kernel

theorem tot1686 : totK PD2M8K2 D2M8K2.t1686 = [0, 0, 67405133671, 337230318051, 394906297940, 79785565037, 1198073392, 0] := by
  decide +kernel

theorem rows1687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1687 = true := by
  decide +kernel

theorem tot1687 : totK PD2M8K2 D2M8K2.t1687 = [0, 0, 0, 199985370207, 454430015705, 174658409650, 11894306413, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
