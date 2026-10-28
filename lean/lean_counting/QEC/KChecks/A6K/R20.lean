import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem rows20 : rowsOKK PA6K tA6K 1955 2053 = true := by
  decide +kernel

end QECKChecks.A6K
