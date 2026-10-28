import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4856 = true := by
  decide +kernel

theorem tot4856 : totK PA10K2 A10K2.t4856 = [0, 612612752922, 1941080745395, 1866127032570, 596121311535, 49180423016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4857 = true := by
  decide +kernel

theorem tot4857 : totK PA10K2 A10K2.t4857 = [0, 464509768748, 1838621391997, 2020276400308, 551484483373, 31080743953, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4858 = true := by
  decide +kernel

theorem tot4858 : totK PA10K2 A10K2.t4858 = [0, 0, 724135188171, 2229592508279, 1605923859499, 267324809227, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows4859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4859 = true := by
  decide +kernel

theorem tot4859 : totK PA10K2 A10K2.t4859 = [0, 472777056719, 1707902366354, 1978952186554, 778488809414, 67593395772, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
