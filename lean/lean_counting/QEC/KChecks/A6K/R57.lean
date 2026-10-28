import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem rows57 : rowsOKK PA6K tA6K 5573 5671 = true := by
  decide +kernel

end QECKChecks.A6K
