import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem rows11 : rowsOKK PA6K tA6K 1075 1173 = true := by
  decide +kernel

end QECKChecks.A6K
