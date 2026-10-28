import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6716 = true := by
  decide +kernel

theorem tot6716 : totK PA10K2 A10K2.t6716 = [350469507776, 1490302209725, 1964075527367, 931478300076, 161248535244, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6717 = true := by
  decide +kernel

theorem tot6717 : totK PA10K2 A10K2.t6717 = [234501307853, 1366113555416, 2156896145920, 908394619479, 58241515735, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6718 = true := by
  decide +kernel

theorem tot6718 : totK PA10K2 A10K2.t6718 = [489082083355, 1532369233719, 1753022564410, 921699325362, 186893550872, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6719 = true := by
  decide +kernel

theorem tot6719 : totK PA10K2 A10K2.t6719 = [314234800528, 1563629554399, 2247380275394, 855132968761, 51551640641, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
