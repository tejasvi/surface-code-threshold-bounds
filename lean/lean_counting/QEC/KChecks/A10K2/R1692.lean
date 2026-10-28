import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6768 = true := by
  decide +kernel

theorem tot6768 : totK PA10K2 A10K2.t6768 = [0, 457327470340, 1826296191810, 2007390165902, 564768169349, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6769 = true := by
  decide +kernel

theorem tot6769 : totK PA10K2 A10K2.t6769 = [0, 0, 726322494422, 2105803461815, 1683175552531, 400018437495, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows6770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6770 = true := by
  decide +kernel

theorem tot6770 : totK PA10K2 A10K2.t6770 = [0, 277894402602, 1167707308993, 1881058424529, 1296585264107, 219817812988, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows6771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6771 = true := by
  decide +kernel

theorem tot6771 : totK PA10K2 A10K2.t6771 = [0, 283322952595, 1520194726010, 2183059728870, 809435486582, 46357501817, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
