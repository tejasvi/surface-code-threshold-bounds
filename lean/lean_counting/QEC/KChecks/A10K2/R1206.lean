import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4824 = true := by
  decide +kernel

theorem tot4824 : totK PA10K2 A10K2.t4824 = [462785603557, 1845285762210, 1915719521894, 491352299434, 13149912228, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4825 = true := by
  decide +kernel

theorem tot4825 : totK PA10K2 A10K2.t4825 = [0, 580002179064, 2009482022640, 1729309579991, 400624536657, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4826 = true := by
  decide +kernel

theorem tot4826 : totK PA10K2 A10K2.t4826 = [292130592925, 1245008558238, 1883459662205, 1152909123532, 198908999013, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4827 = true := by
  decide +kernel

theorem tot4827 : totK PA10K2 A10K2.t4827 = [455179774352, 1729335923900, 1902891451822, 550895577947, 31927403898, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
