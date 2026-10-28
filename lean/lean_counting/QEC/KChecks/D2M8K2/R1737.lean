import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6948 = true := by
  decide +kernel

theorem tot6948 : totK PD2M8K2 D2M8K2.t6948 = [0, 162954607221, 461485261294, 265169828247, 21253095941, 0, 0, 0] := by
  decide +kernel

theorem rows6949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6949 = true := by
  decide +kernel

theorem tot6949 : totK PD2M8K2 D2M8K2.t6949 = [0, 0, 229907940073, 496428699519, 159354720962, 4903313894, 0, 0] := by
  decide +kernel

theorem rows6950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6950 = true := by
  decide +kernel

theorem tot6950 : totK PD2M8K2 D2M8K2.t6950 = [0, 0, 177545344912, 474204228722, 211793204329, 9951379744, 0, 0] := by
  decide +kernel

theorem rows6951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6951 = true := by
  decide +kernel

theorem tot6951 : totK PD2M8K2 D2M8K2.t6951 = [0, 195722704776, 467235194779, 203773728612, 26641439224, 7075888420, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
