import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1132 = true := by
  decide +kernel

theorem tot1132 : totK PD2M8K2 D2M8K2.t1132 = [0, 0, 203394830628, 483852619998, 211740438164, 12531227089, 0, 0] := by
  decide +kernel

theorem rows1133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1133 = true := by
  decide +kernel

theorem tot1133 : totK PD2M8K2 D2M8K2.t1133 = [0, 85737809554, 309071400053, 385078855908, 114921295221, 2535105584, 0, 0] := by
  decide +kernel

theorem rows1134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1134 = true := by
  decide +kernel

theorem tot1134 : totK PD2M8K2 D2M8K2.t1134 = [0, 180391776741, 465905914976, 249625955910, 22155395302, 0, 0, 0] := by
  decide +kernel

theorem rows1135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1135 = true := by
  decide +kernel

theorem tot1135 : totK PD2M8K2 D2M8K2.t1135 = [0, 171160235349, 474571769391, 246324420393, 13598106836, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
