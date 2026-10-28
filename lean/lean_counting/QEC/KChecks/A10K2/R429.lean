import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1716 = true := by
  decide +kernel

theorem tot1716 : totK PA10K2 A10K2.t1716 = [0, 0, 0, 0, 567665805405, 1964888562227, 1672332402216, 399605066241, 25239774317, 0] := by
  decide +kernel

theorem rows1717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1717 = true := by
  decide +kernel

theorem tot1717 : totK PA10K2 A10K2.t1717 = [0, 0, 0, 318493191224, 1336655561668, 1952164572275, 992339265155, 168617086632, 5410721913, 0] := by
  decide +kernel

theorem rows1718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1718 = true := by
  decide +kernel

theorem tot1718 : totK PA10K2 A10K2.t1718 = [0, 0, 0, 417616870053, 1729524967020, 1890384464591, 487546810027, 32744407728, 0, 0] := by
  decide +kernel

theorem rows1719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1719 = true := by
  decide +kernel

theorem tot1719 : totK PA10K2 A10K2.t1719 = [0, 0, 0, 185564004214, 1033425107751, 1985942093220, 1159352181071, 172144795134, 5546304973, 0] := by
  decide +kernel

end QECKChecks.A10K2
