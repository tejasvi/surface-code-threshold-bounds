import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem size : tA6K.toList.length = 6258 := by
  decide +kernel

theorem start : startOKK PA6K tA6K = true := by
  decide +kernel

end QECKChecks.A6K
