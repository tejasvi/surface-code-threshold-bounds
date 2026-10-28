import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11144 = true := by
  decide +kernel

theorem tot11144 : totK PD2M8K2 D2M8K2.t11144 = [0, 88927555957, 383024479316, 396621562064, 49840983551, 0, 0, 0] := by
  decide +kernel

theorem rows11145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11145 = true := by
  decide +kernel

theorem tot11145 : totK PD2M8K2 D2M8K2.t11145 = [0, 185462505591, 464703560442, 236657677298, 16616745734, 0, 0, 0] := by
  decide +kernel

theorem rows11146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11146 = true := by
  decide +kernel

theorem tot11146 : totK PD2M8K2 D2M8K2.t11146 = [0, 55940259089, 338240742083, 433799675645, 92882423112, 2860976293, 0, 0] := by
  decide +kernel

theorem rows11147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11147 = true := by
  decide +kernel

theorem tot11147 : totK PD2M8K2 D2M8K2.t11147 = [0, 86934566719, 304131803088, 387354206438, 113436998602, 2423372772, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
