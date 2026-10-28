import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem rows13 : rowsOKK PA6K tA6K 1271 1368 = true := by
  decide +kernel

end QECKChecks.A6K
