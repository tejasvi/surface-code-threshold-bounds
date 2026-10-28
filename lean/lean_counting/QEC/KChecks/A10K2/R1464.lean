import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5856 = true := by
  decide +kernel

theorem tot5856 : totK PA10K2 A10K2.t5856 = [0, 0, 0, 490383956341, 1839335436366, 1927508302118, 445685921643, 24194100374, 0, 0] := by
  decide +kernel

theorem rows5857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5857 = true := by
  decide +kernel

theorem tot5857 : totK PA10K2 A10K2.t5857 = [0, 0, 0, 0, 644055266502, 2002302786877, 1517516177872, 343023357247, 25130442608, 0] := by
  decide +kernel

theorem rows5858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5858 = true := by
  decide +kernel

theorem tot5858 : totK PA10K2 A10K2.t5858 = [0, 0, 0, 480609670417, 1776878028040, 1772013107618, 584552237832, 107532928520, 5517381808, 0] := by
  decide +kernel

theorem rows5859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5859 = true := by
  decide +kernel

theorem tot5859 : totK PA10K2 A10K2.t5859 = [0, 0, 0, 296338766410, 1549460224370, 2118266301086, 701590330792, 44279266706, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
