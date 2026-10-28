import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3856 = true := by
  decide +kernel

theorem tot3856 : totK PA10K2 A10K2.t3856 = [0, 0, 0, 480454151645, 1777811773793, 1867126081615, 552285119350, 37254374173, 0, 0] := by
  decide +kernel

theorem rows3857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3857 = true := by
  decide +kernel

theorem tot3857 : totK PA10K2 A10K2.t3857 = [0, 0, 0, 295075171265, 1531137538323, 2156488481587, 714196487168, 39127887026, 0, 0] := by
  decide +kernel

theorem rows3858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3858 = true := by
  decide +kernel

theorem tot3858 : totK PA10K2 A10K2.t3858 = [0, 0, 0, 284548233047, 1209391152940, 1887199761689, 1130881980001, 198646936797, 6354482628, 0] := by
  decide +kernel

theorem rows3859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3859 = true := by
  decide +kernel

theorem tot3859 : totK PA10K2 A10K2.t3859 = [0, 0, 0, 499321699658, 1854388686349, 2010688879657, 570125437929, 42439808068, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
