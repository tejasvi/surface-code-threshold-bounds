import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem rows22 : rowsOKK PA6K tA6K 2151 2248 = true := by
  decide +kernel

end QECKChecks.A6K
