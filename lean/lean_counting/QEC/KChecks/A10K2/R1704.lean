import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6816 = true := by
  decide +kernel

theorem tot6816 : totK PA10K2 A10K2.t6816 = [227773083334, 1246127070503, 2169548989587, 1257319050787, 155401513081, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6817 = true := by
  decide +kernel

theorem tot6817 : totK PA10K2 A10K2.t6817 = [166777988200, 876052248449, 1792874116273, 1529627726609, 417858097259, 30428024596, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6818 = true := by
  decide +kernel

theorem tot6818 : totK PA10K2 A10K2.t6818 = [458361818573, 1752904814243, 2053192495152, 660632974989, 47509261575, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6819 = true := by
  decide +kernel

theorem tot6819 : totK PA10K2 A10K2.t6819 = [256497644603, 1401065832279, 2224663154477, 1090024937714, 114236434292, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
