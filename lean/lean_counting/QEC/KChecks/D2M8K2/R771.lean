import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3084 = true := by
  decide +kernel

theorem tot3084 : totK PD2M8K2 D2M8K2.t3084 = [0, 159406523291, 467719140189, 282835713811, 28951919202, 0, 0, 0] := by
  decide +kernel

theorem rows3085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3085 = true := by
  decide +kernel

theorem tot3085 : totK PD2M8K2 D2M8K2.t3085 = [0, 0, 174127047059, 442712505181, 253775803492, 23322377560, 0, 0] := by
  decide +kernel

theorem rows3086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3086 = true := by
  decide +kernel

theorem tot3086 : totK PD2M8K2 D2M8K2.t3086 = [0, 0, 206756776882, 518542828077, 186804413891, 2655503019, 0, 0] := by
  decide +kernel

theorem rows3087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3087 = true := by
  decide +kernel

theorem tot3087 : totK PD2M8K2 D2M8K2.t3087 = [0, 171120547633, 414367477158, 231780536768, 71379239607, 5598539909, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
